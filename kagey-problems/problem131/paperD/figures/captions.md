# Figure captions for Paper D

Paper D has two figures, both 6.4 in wide and drawn in the shared style of `../../figures/series_style.py`.
Figure 1 is made by `make_family_figure.py` (under a second) and Figure 2 by `make_figures.py` in this
folder. Each is included with `\includegraphics[width=\textwidth]{figures/...}`. The script
`make_figures.py` also makes `crossing.pdf`, a figure of the elephant crossing that the paper no longer
prints (Table 1 has its numbers), and it writes the figure `heavy` of Paper F to `../../paperF/figures`.

## Figure 1, `family.pdf`, label `fig:family`, at the start of Section 3.1 before Lemma 3.1

One elephant walk with $N=40$ steps and $\varepsilon=0.07$. (a) The position against the step. The steps that disagree with the first step are drawn in blue. (b) The memory tree of the same walk. Step $k+1$ copies the step at the left end of its arc, and the arcs drawn heavier are flips. A step disagrees with the first step exactly when the path from it to step $1$ crosses an odd number of flips (Lemma~\ref{lem:tree}). The first flip, at step $4$, turns its family of ten steps. The flip at step $22$, inside that family, turns its own family of three steps back, and the flip at step $39$ turns only that step.

## Figure 2, `shape.pdf`, label `fig:shape`, in Section 3.2 before Theorem 3.15

The elephant walk at its crossing. (a) The law $P_N$ for $N=3200$ at its crossing $x=11.5468$, divided by the end $E_N$. The center equals the end, and the law rises from each end to a mode and falls to the center. The inset shows the last 60 bins, with dots at bins $N$, $N-1$ and $N-2$. The end is below its neighbor, and the modes are 25 steps from each end (dashed). (b) The law of $M_N$, scaled as $xf_N(m)$, against $\lambda_m=(m-x\log x)/x$, with the Landau density $f_L$. The dotted line is its mode $\lambda_0$. (c) The tail $P_N(N-m)$ divided by $x/(2m^2)$. The dashed line is the limit 1 of Theorem~\ref{thm:profile}, and the dotted curves are the heuristic correction $1+x(2\log m+2\gamma-3)/m$ for $2x\log x\le m\le N/x$. The rise of the $N=3200$ curve near $m=N/2$ is the mirror term $f_N(N-m)$. At $N=10^6$ we use $x=g_N=22.4407$.
