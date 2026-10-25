# 15. Framing and vocabulary pass (Paper F and the coin-turning note)

October 24, 2026. Folders touched: `kagey-problems/problem131/paperF` and
`kagey-problems/problem131/S4_aging_note`. Nothing else was edited.

Rules applied to both papers. The motivating problem appears once, in the acknowledgments. No paper
is called part of a series. Companion papers get one sentence or clause. Standard probability
words replace "bin" and "row". The first paragraph states the law of the count and the main
theorem.

## Paper F (EJP)

### Vocabulary

- "bin" or "bins" in the TeX source went from 61 to 0. Each was replaced by "point", "value",
  "point mass", "atom" (for the two endpoints), "contribution" (for the terms of the giant-run
  split in Section 4) or by $P_N(k)$ itself.
- "row" in the TeX source went from 17 to 0 (including "whole-row error" and "whole-row
  criterion"). It became "the range $\{0,\dots,N\}$", "the range of the count", "the whole range"
  or "the law".
- The label `eq:bulk-remote-bins` became `eq:bulk-remote-points` (both uses are in `sec_bulk.tex`,
  and no script, map or note outside the folder used it). The paragraph heading "Step 4. Remote
  bins." became "Step 4. Remote points.".
- Outside the TeX: `README.md` (5 bin, 3 row), `figures/captions.md` (1), the docstring and a
  comment of `figures/make_atlas_figure.py` (1 row, 1 bin), the docstring of `certify_antimode.py`
  (1) and the printed check label 5a of `verify_coefficient.py` (1). No macro contained the word.
  The remaining "row" in the scripts are Python names for table rows and a matrix row sum, not
  prose.
- Left unchanged on purpose: `figures/numbers_for_verify.md` quotes removed passages "word for
  word" and keeps its 2 "bins" and 2 "row" as historical record.

### Abstract (219 words by `wc -w`, about 215 of text)

> A lattice Lévy walk moves in runs of alternating direction whose lengths are independent with
> regularly varying tails of index between 1 and 2. We describe the law of the number of right
> steps after N steps at every point. It has four pieces, a stable bulk, a big-jump zone on each
> side, a renewal boundary layer at each end and an atom at each endpoint. Together they give a
> rigorous lattice version of the infinite density of the Lévy walk, with its boundary layer and
> endpoint atoms. In the bulk a local limit theorem holds uniformly over the whole range of the
> count, with a bound of the bulk order at every point, under regular variation and aperiodicity
> alone. The big-jump zone and the boundary layer are given by one exact kernel, the sum of a
> complete giant run and a run cut by the horizon. This kernel needs the local form of regular
> variation, and regular variation of the tail does not suffice. If the two run scales differ by
> an unbounded factor, one window is described only in part. We also give the exact effect of the
> first run on each piece, the global mode with its golden ratio threshold, the interior minimum
> near an end, and the identification of both run laws from the ends.

The labels "Theorem A" and "Theorem B" are gone from the abstract. "one and two" became digits.

### Introduction

- The first paragraph now runs: model, the law $P_N(k)$ on $\{0,\dots,N\}$, "We describe $P_N(k)$
  at every point", the bulk theorem (Theorem A), the one-kernel big-jump theorem (Theorem B), and
  that read at $k=vN$ this kernel is a rigorous lattice version of the infinite density of the
  Lévy walk with its boundary layer and endpoint atoms. The physics context (superdiffusion, heat
  transport, occupation times, side peaks) follows. The paragraph never mentions the motivating
  question.
- The paragraph "This series" (ending "the heavy-tailed member of the series") is deleted. Papers
  A and D are not used in any proof, so they now get one clause in the paragraph "The walk" of the
  related work: "and for geometric run lengths its crossings and a related walk with a Landau
  profile are treated in [paperA, paperD]".
- The acknowledgments now read "I thank Peter Kagey, whose Problem 131 in his Open Problem
  Collection [kagey131] started this work, and Aidan Deshong for insightful conversations." This
  is the only mention of the problem. The source comment "Paper F of Problem 131" on line 2 of
  `problem131_levy.tex` was dropped too.

### Build and scripts

- `pdflatex problem131_levy.tex` three times: 55 pages, no undefined references, no multiply
  defined labels, no overfull boxes. Two underfull vboxes (pages 5 and 49, float placement) remain,
  as in the earlier builds.
- `py -I verify_all.py --full`: all 6 scripts pass (1.3 min). Then `py -I figures/make_atlas_figure.py`
  (zone errors 0.071, 0.38, 0.094, unchanged) and `py -I verify_all.py`: all 4 pass. Every output
  in `data/` and the figure were rewritten with fresh sha256 headers. New hashes:
  `certify_antimode.py` 9ced1088..., `verify_coefficient.py` 6276fb8b.... The others are
  unchanged (`certify_atlas.py` e2a903c5..., `verify_identities.py` 70d46dde...,
  `verify_preparation.py` 50b093fe..., `verify_bigjump.py` e9ff661d...). Neither README nor
  `sec_verify.tex` quotes a script hash, so no text needed updating.

## The coin-turning note (ECP)

### Title, class and length

- New title "The finite-size shape transition of coin-turning walks" in `\TITLE`, `\SHORTTITLE`,
  the pdftitle (set by `\hypersetup` after `\begin{document}`, since the class leaves it unset in
  preprint mode), `README.md`, the docstrings of `verify_aging.py` and `verify_aging_urn.py`, and
  the printed header of `verify_aging.py`.
- The note was in `article`. It now uses `\documentclass[ECP,preprint]{ejpecp}` with `\TITLE`,
  `\AUTHORS`, `\KEYWORDS`, `\AMSSUBJ` (60J10, 60F05; secondary 60C05, 60G50), `\ABSTRACT` and the
  class theorem environments and `acks`. The packages the class already loads were removed, and
  only `enumitem` is added. The bibliography was rewritten in the EJP/ECP style of the class
  sample, in alphabetical order. No MR numbers were added (none were at hand, and none were
  invented). The citation of Godrèche and Luck was dropped with the sentence on "aging".
- Page limit. The class documentation (`ejpecp.pdf`, `sample.tex`) states none. The ECP
  submission page (https://emis.dsd.sztaki.hu/journals/EJP-ECP/_ejpecp/ECP/submissions.html) says
  research articles "should normally be 12 pages or less in length", and IMS pages describe ECP as
  the venue for papers under 12 pages. The journal page at imstat.org could not be read (bot
  check). The build has 12 pages, so the note is at the limit. This is recorded in the README.

### Vocabulary and framing

- "bin" in the TeX went from 30 to 0. It became "point", "value", "mass of the point $k$" for the
  count $A_N$, and "count vector" for the $d$-state chain. The sentence "We call them bins." was
  deleted. Printed labels of `verify_aging.py` and the docstring of `figures/make_aging_figure.py`
  were changed the same way. The Python names `bins` and `nbins` stay.
- The opening "A walk on Z that moves in runs of one direction reaches an end bin only if ...",
  the Kagey sentence, "This note is part of a series on Problem 131" and "Here the walk ages" are
  gone. The companion papers A and B now share one sentence at the end of the prior work. The
  citation of paper B in Remark 2.5 now points to that sentence (Section 1.3). Kagey appears only
  in the new acknowledgments.

### Abstract (188 words by `wc -w`)

> A coin-turning walk on the integers switches direction at step k with probability c/k. With a
> fair first step the fraction of right steps converges in law to Beta(c,c), which is U-shaped
> for c<1, uniform at c=1 and peaked at the center for c>1. We locate this shape transition at
> finite N. With a fixed first step it happens exactly at c=1 for every N. The number of right
> steps is then uniform on {1,...,N}, and the ratio of the mass of each interior point to that of
> the end increases strictly in c, so every interior point ties with the end at c=1. The same
> holds for a walk on d states, whose count vector is uniform at the tie. Both laws come from a
> chain that draws its state afresh or repeats it, and we give the joint law of its counts and
> last state for every weight. With a fair first step the center ties with the end at
> c_N = 1 - log 2/(log N + gamma + 2 - 2 log 2) + O((log N)^(-3)), where gamma is Euler's
> constant. The proof rests on a local limit theorem with a rate for the Beta(c,c) density at the
> center.

The first paragraph of the introduction follows the same line. It gives the walk, the Beta(c,c)
limit and its shape transition at c=1, the question of where the transition happens at finite N,
and the two answers (exactly c=1 with a fixed start, Proposition 2.3, and c_N<1 with
1-c_N ~ log 2/log N with a fair start, Proposition 2.7), then the d-state walk (Theorem 2.4).

### Build and scripts

- `pdflatex s4_note.tex` three times: 12 pages, no undefined references, no multiply defined
  labels, no overfull or underfull boxes. Two fixes were needed. A display replaced an inline sum
  in Step 4 of the proof of Proposition A.3, and `\nolinkurl` replaced `\texttt` for the script
  names in the Verification paragraph (the old `\sloppy` group is gone).
- `py -I verify_aging.py`: all checks pass (30 s). `py -I verify_aging_urn.py`: both checks True.
  Its output is identical to `data/verify_aging_urn_output.txt`, which has no hash header.
  New sha256: `verify_aging.py` cbd1f845..., `verify_aging_urn.py` e7824c51...,
  `figures/make_aging_figure.py` 6837d905... (docstring only, figure not redrawn). The README
  hashes were updated.

## Edits needed outside the two folders

1. `kagey-problems/problem131/README.md`, line 176. It gives the old title "When the end ties the
   center in a coin-turning walk" and says "Every interior bin ties with the end". Suggested text:
   "`S4_aging_note/` is a short note, "The finite-size shape transition of coin-turning walks",
   on the walk that switches at step k with probability c/k and its version with d states. Every
   interior point ties with the end exactly at c = 1 for every N, ..."
2. `kagey-problems/problem131/lean/PaperD/MAP.md` still lists the note's statements under the old
   Paper F numbers and path (already noted in the note's README).
3. The hashes of the two note scripts recorded in the two `research_notes` JSON files named in the
   note's README match the archived copies, not the current ones (unchanged situation, new hashes).

## Points for the author

- Both papers keep a software-availability sentence with the repository URL
  `https://github.com/apemm/Kagey-Problems` and the path `kagey-problems/problem131/...`. The
  name appears there as a repository name, not as the motivating problem. Renaming or using an
  archive DOI would remove it if a second appearance is unwanted.
- The acknowledgments of both papers use "I", as Paper F already did. Changing them to "We" is a
  one-word edit.
- The note is at the 12-page ECP guideline. Any addition needs a matching cut.
