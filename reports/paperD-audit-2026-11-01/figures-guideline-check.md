# Paper D figure check against the JTP artwork guidelines

Checked 1 November 2026 against the [Journal of Theoretical Probability submission guidelines](https://link.springer.com/journal/10959/submission-guidelines), particularly Artwork and Illustrations Guidelines.

Both active figures now have native vector EPS submission files, `Fig1.eps` and `Fig2.eps`, and PDF aliases `Fig1.pdf` and `Fig2.pdf`. Compatible `family.pdf` and `shape.pdf` names remain. The Python/Matplotlib scripts reproduce the exports; the existing cache is sufficient for Figure 2 with `--shape-only`.

| Check | Figure 1 | Figure 2 |
|---|---:|---:|
| Exported width, inches | 5.3754 | 6.5391 |
| Base lettering at 6.4-inch manuscript width, pt | 10.12 | 8.32 |
| Thinnest nonzero stroke at that width, pt | 0.595 | 0.489 |
| Embedded fonts | DejaVu Sans, regular and oblique | DejaVu Sans, regular and oblique |
| Native EPS embedded font format | Type 42 | Type 42 |

Base lettering is 8.5 pt before scaling; mathematical subscripts and superscripts use the normal 70% script size. Text is black or `#1F2328`; the latter has 15.80:1 contrast on white, exceeding the guideline's 4.5:1 threshold. The EPS files use RGB drawing commands and contain no raster image operators. PDF fonts are embedded TrueType subsets. There are no semitransparent visible objects; fully absent patch edges appear as zero stroke alpha in the PDFs. EPS generation emitted no transparency warning and requires no flattening.

I inspected rendered colour and greyscale versions of both updated PDFs. The plots remain distinguishable by line weights, markers and dash patterns. The family annotation is now dark text over an opaque white background, and faint context arcs were darkened. There are no embedded titles or captions. Panel letters are lowercase. The caption record describes line styles without requiring colour.

The N=3200 data cache retains SHA-256 `03f745ace8a0a268923e9ddb58120783d435bf013deb7a0e45a2e22beb0e88d9`. The tree still has flips at steps 4, 22 and 39, with the first family containing ten steps. No mathematical data, shared style files or Paper F outputs changed. `git diff --check` passes.

This check uses the current 6.4-inch manuscript inclusion width. If production resizes the figures, lettering should be checked again at the requested final size.
