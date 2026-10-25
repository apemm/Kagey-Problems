# 19. Cuts to Paper C1 before arXiv

October 24, 2026. We made three cuts to Paper C1 (`kagey-problems/problem131/paperC`) before it
goes to arXiv as version 2 of arXiv:2610.09258. Nothing else was cut. The tree formula
(Proposition 5.11, Appendix A.7), Examples 5.13 and 5.14, Section 3.2, the uniform face maxima
(now Section 5.6 and Proposition 5.15), Section 6, Section 8 and Appendix D are unchanged.

## What was removed

1. The weak field.
   - Section 5.6 (`sec:weakfield`) with Proposition 5.15 (`prop:weakfield`), its setup and its
     proof. The section held nothing else.
   - Section 7.4 (`sec:complete-field`) with Corollary 7.11 (`cor:weakfield-phases`), Corollary
     7.12 (`cor:weakfield-full-hierarchy`) and equations (24) and (25) (`eq:weakfield-maximum`,
     `eq:weakfield-lines`).
   - Panel (b) of Figure 1 (`fig:complete-envelope`). `figures/make_complete_envelope.py` now draws
     panel (a) only, at 280 points wide, and the figure is included at 0.62 of the text width. The
     caption in `sec_intro.tex` and in `figures/captions.md` now describes one panel.
   - In the introduction, the clause on the weak field after Theorem B and the sentences after
     Theorem C on a start law and a weak field. In Section 5 the opening list no longer names
     Section 5.6.
2. The start. Section 7.3 (`sec:start`) with Corollary 7.9 (`cor:start-crossings`), Example 7.10
   (`ex:K3-start`) and the sentence on Lean after it. Its sentence in the introduction went with
   the cut of item 1.
3. Section 9. `sec_verify.tex` now says what is checked, how to run it and where the code and the
   outputs are, in under a page (page 46 of the article build, with the open questions). The
   sentence that the older scripts were written for an earlier version is gone. The text names the
   7 scripts that `verify_all.py` runs.

A search of all section, appendix and main files found no other use of the removed labels, of
`\widetilde P_{N,\xi}`, `w_\xi` or `M^\xi_F`, or of the results of Sections 5.6, 7.3 and 7.4.
The removed text cited only `paperB`, which is cited elsewhere, so no bibliography entry was
removed. All 38 entries are still cited. The abstract did not mention the weak field or the
start and is unchanged.

## Renumbering (both builds, from the `.aux` files)

| Label | Before | After |
|---|---|---|
| `sec:uniform-class` | Section 5.7 | Section 5.6 |
| `prop:uniform-facemax` | Proposition 5.16 | Proposition 5.15 |
| `eq:uniform-laguerre-bessel` | (26) | (24) |
| `eq:vertex-uniform-bracket` | (27) | (25) |
| `eq:vertex-uniform-root` | (28) | (26) |
| article build only: `eq:A-dirichlet` to `eq:vertex-tangent-upper` | (29) to (41) | (27) to (39) |

So `eq:A-radii` is (29) in the article build (was 31), and still A3 in the Springer build. Every
other statement kept its number, including all of Sections 6, 7.1, 7.2 and 8 and the appendices.

## Dependent files

- Paper C2. Its only C1 number that moved is `\cite[Proposition~5.16]{paperC1}` in
  `sec_reversible.tex` 275, now Proposition 5.15. `paperC2/README.md` says the same. C2 was
  rebuilt 3 times with no undefined or multiply defined reference and no overfull box (41 pages).
- `EXPORTS.md`. A dated note at the top, `prop:uniform-facemax` now Proposition 5.15, Section 5.6
  for `sec:uniform-class`, and equation (29) for `eq:A-radii`.
- Scripts. `verify_weak_field.py` and `data/verify_weak_field_output.txt` were deleted and removed
  from `verify_all.py`. `verify_second_order.py` lost `check_K3_window` (the check of Example 7.10
  and of the ends of the edge window at finite N), and one check label no longer names that window.
  It was rerun through `verify_all.py`, which refreshed its output with the sha256 header. No other
  script checked Sections 5.6, 7.3 or 7.4.
- `lean/PaperC/MAP.md`. The rows for Example 7.10 and Corollaries 7.11 and 7.12 moved to a new
  section "Statements cut from C1 on October 24, 2026", with the Lean theorems kept. Proposition
  5.16 is now 5.15 under "Not in Lean", the cut statements left that list and the list of
  differences, the C1 equation numbers from (26) on moved down by 2, and the page counts are 67,
  72 and 41. No Lean docstring cites a C1 number that moved, so no Lean file changed.
- `paperC/README.md`, `figures/captions.md`, the top-level `problem131/README.md` and
  `problem131/verify_all.py`. Page counts, script counts, the summary of results, the removed
  labels and a line of history. The cover letter does not mention the cut material or a page
  count and is unchanged.

## Builds and checks

- `problem131_chains.tex`, 3 runs: 67 pages (was 70). No undefined reference, no multiply defined
  label, no overfull box.
- `problem131_chains_sn.tex`, with `TEXINPUTS=".;../common/sn-jnl;"`: 72 pages (was 77), clean
  after the label pass settled.
- `py -I verify_all.py --quick` in `paperC`: 7 of 7 scripts passed in 539 s. Each output in `data/`
  was rewritten with its sha256 header.

One file outside the write scope still says 70 pages, the comment field in
`18_arxiv_form_C1.txt`. It should read 67 pages when the form is submitted.
