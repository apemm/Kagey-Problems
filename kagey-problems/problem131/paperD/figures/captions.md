# Figure captions for Paper D

Paper D has two figures, each drawn on a 6.4 in canvas and included at the manuscript text width. Local typography overrides use 8.5 pt DejaVu Sans base lettering and embedded fonts. Tight cropping makes the exported widths differ from the canvas widths; at a 6.4 in inclusion width, base lettering is 10.12 pt in Figure 1 and 8.32 pt in Figure 2.
Figure 1 is made by `make_family_figure.py` (under a second) and Figure 2 by `make_figures.py` in this
folder. Use `python -B make_figures.py --shape-only` to redraw Figure 2 from its existing cache without touching Paper F.
The submission files are `Fig1.pdf`, `Fig2.pdf`, `Fig1.eps` and `Fig2.eps`. The EPS files are native vector exports with embedded Type 42 fonts. The scripts also retain the compatible names `family.pdf` and `shape.pdf`, with 600 dpi PNG previews. The EPS/PDF files, rather than the PNG previews, are the submission artwork. All drawing is opaque; no transparency flattening is needed. Figures were generated with Python and Matplotlib.
Each is included with `\includegraphics[width=\textwidth]{figures/...}`. The script
`make_figures.py` also makes `crossing.pdf`, a figure of the elephant crossing that the paper no longer
prints (Table 1 has its numbers), and it writes the figure `heavy` of Paper F to `../../paperF/figures`.

## Figure 1, `Fig1.pdf`, label `fig:family`, at the start of Section 3.1 before Lemma 3.1

One elephant walk with $N=40$ steps and $\varepsilon=0.07$. (a) The position against the step. The steps that disagree with the first step are drawn heavier. (b) The memory tree of the same walk. Step $k+1$ copies the step at the left end of its arc, and the arcs drawn heavier are flips. A step disagrees with the first step exactly when the path from it to step $1$ crosses an odd number of flips (Lemma~\ref{lem:tree}). The first flip, at step $4$, turns its family of ten steps. The flip at step $22$, inside that family, turns its own family of three steps back, and the flip at step $39$ turns only that step

## Figure 2, `Fig2.pdf`, label `fig:shape`, in Section 3.2 before Theorem 3.5

The count axis uses `k`, reserving `a` for the fixed-memory parameter. The `N=3200`
curve is dash-dot in both panels (b) and (c); `N=10^6` is dashed.
The dotted curves in (c) remain heuristic corrections, not certified bounds.

The elephant walk at its crossing. (a) The law $P_N$ for $N=3200$ at its crossing $x=11.5468$, divided by the end $E_N$. The center equals the end, and the law rises from each end to a mode and falls to the center. The inset shows the last 60 values, with dots at $N$, $N-1$ and $N-2$. The end is below its neighbor, and the modes are at distance 25 from each end (dashed). (b) The law of $M_N$, scaled as $xf_N(m)$, against $\lambda_m=(m-x\log x)/x$, with the Landau density $f_L$. The dotted line is its mode $\lambda_{\mathrm L}$. (c) The tail $P_N(N-m)$ divided by $x/(2m^2)$. The dashed line is the limit 1 of the tail theorem in the arXiv version of the paper (Theorem S2.1 there), and the dotted curves are the heuristic correction $1+x(2\log m+2\gamma-3)/m$ for $2x\log x\le m\le N/x$. The rise of the $N=3200$ curve near $m=N/2$ is the mirror term $f_N(N-m)$. At $N=10^6$ we use $x=g_N=22.4407$.
