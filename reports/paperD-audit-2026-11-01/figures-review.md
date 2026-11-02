# Paper D figure check

Both figures were rendered and inspected at their printed aspect ratios on November 1, 2026.

Figure 1 is readable and its paired path/tree diagram explains the descendant-family argument.
No visual change was needed. Its fixed seed produces flips at steps 4, 22 and 39, with family
sizes 10, 3 and 1, matching the caption. The script's stale description as Figure 2 was corrected.

Figure 2 received three small improvements:

- The count variable on panel (a) and its inset is now `k`, matching the main notation and
  avoiding confusion with the fixed-memory parameter `a`.
- The `N=3200` curve uses the same dash-dot style in panels (b) and (c).
- The light gold curve is now darker vermilion, improving contrast against white paper.
  The purple curve and distinct line styles remain, so color is not the only cue.

The plotted data did not change. The cache SHA-256 remains
`03f745ace8a0a268923e9ddb58120783d435bf013deb7a0e45a2e22beb0e88d9`.
The cached 3200-step curve was compared with a fresh forward recurrence. Its maximum relative
difference was `5.03e-12`; the center/end ratio was 1 and the left mode was at 25, as captioned.
No million-step simulation was repeated.

The revised PDF was rendered and checked after regeneration. No labels overlap or clip.
The curve labelled heuristic remains dotted and is not presented as a certified bound.
The caption already states that the million-step curve uses the approximate crossing `x=g_N`.

`make_figures.py --shape-only` now regenerates only this figure from the existing cache, without
rebuilding historical crossing plots or writing any Paper F files. The script documentation and
`figures/captions.md` describe this command. No Paper F output was changed.
